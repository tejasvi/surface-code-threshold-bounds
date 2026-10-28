import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14912 = true := by
  decide +kernel

theorem tot14912 : totK PD2M8K2 D2M8K2.t14912 = [0, 179096909081, 383692368091, 213371635124, 112681798607, 13326740810, 0, 0] := by
  decide +kernel

theorem rows14913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14913 = true := by
  decide +kernel

theorem tot14913 : totK PD2M8K2 D2M8K2.t14913 = [0, 167936292315, 449223232790, 246377798923, 18049822406, 0, 0, 0] := by
  decide +kernel

theorem rows14914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14914 = true := by
  decide +kernel

theorem tot14914 : totK PD2M8K2 D2M8K2.t14914 = [0, 88680480173, 367682532896, 368724371998, 74496607326, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14915 = true := by
  decide +kernel

theorem tot14915 : totK PD2M8K2 D2M8K2.t14915 = [0, 0, 320206340722, 512892858803, 68995250722, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
