import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8704 = true := by
  decide +kernel

theorem tot8704 : totK PD2M8K2 D2M8K2.t8704 = [0, 0, 170019870284, 433843103834, 266167964907, 26962658215, 0, 0] := by
  decide +kernel

theorem rows8705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8705 = true := by
  decide +kernel

theorem tot8705 : totK PD2M8K2 D2M8K2.t8705 = [0, 0, 91986061513, 428231647452, 345458244860, 34691941931, 0, 0] := by
  decide +kernel

theorem rows8706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8706 = true := by
  decide +kernel

theorem tot8706 : totK PD2M8K2 D2M8K2.t8706 = [0, 0, 0, 220740764420, 497570429231, 140806342702, 2437267027, 0] := by
  decide +kernel

theorem rows8707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8707 = true := by
  decide +kernel

theorem tot8707 : totK PD2M8K2 D2M8K2.t8707 = [0, 119216023376, 270757075700, 224228066740, 192663523558, 91712697100, 6701800220, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
