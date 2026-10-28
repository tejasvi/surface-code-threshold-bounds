import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14388 = true := by
  decide +kernel

theorem tot14388 : totK PD2M8K2 D2M8K2.t14388 = [0, 72246768061, 341402665905, 387279534987, 83223317602, 1164319620, 0, 0] := by
  decide +kernel

theorem rows14389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14389 = true := by
  decide +kernel

theorem tot14389 : totK PD2M8K2 D2M8K2.t14389 = [0, 0, 230651639607, 489421093528, 159920433329, 9404247146, 0, 0] := by
  decide +kernel

theorem rows14390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14390 = true := by
  decide +kernel

theorem tot14390 : totK PD2M8K2 D2M8K2.t14390 = [0, 167889516001, 406054888014, 262006666486, 52994899279, 2481160468, 0, 0] := by
  decide +kernel

theorem rows14391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14391 = true := by
  decide +kernel

theorem tot14391 : totK PD2M8K2 D2M8K2.t14391 = [0, 163418506481, 440644428512, 277186624991, 29737804969, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
