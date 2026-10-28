import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11120 = true := by
  decide +kernel

theorem tot11120 : totK PD2M8K2 D2M8K2.t11120 = [0, 36594270515, 205861051592, 425507579555, 173091789910, 11894306413, 0, 0] := by
  decide +kernel

theorem rows11121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11121 = true := by
  decide +kernel

theorem tot11121 : totK PD2M8K2 D2M8K2.t11121 = [0, 203537535603, 472306851482, 214722164746, 9745156230, 0, 0, 0] := by
  decide +kernel

theorem rows11122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11122 = true := by
  decide +kernel

theorem tot11122 : totK PD2M8K2 D2M8K2.t11122 = [0, 175892744135, 456424228704, 237716783519, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows11123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11123 = true := by
  decide +kernel

theorem tot11123 : totK PD2M8K2 D2M8K2.t11123 = [0, 0, 308354184805, 494614587051, 79378731373, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
