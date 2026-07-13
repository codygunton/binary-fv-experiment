import Lake

open Lake DSL

package sszBridge

lean_lib SszBridge

lean_exe ssz_bridge where
  root := `SszBridge.Main

lean_exe ssz_bridge_test where
  root := `SszBridgeTest
