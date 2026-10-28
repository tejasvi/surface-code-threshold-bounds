import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6824 = true := by
  decide +kernel

theorem tot6824 : totK PD2M8K2 D2M8K2.t6824 = [0, 176380083289, 468727455613, 246978275263, 13761953177, 0, 0, 0] := by
  decide +kernel

theorem rows6825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6825 = true := by
  decide +kernel

theorem tot6825 : totK PD2M8K2 D2M8K2.t6825 = [0, 88734372665, 356703116358, 360445442373, 71424798437, 1162935789, 0, 0] := by
  decide +kernel

theorem rows6826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6826 = true := by
  decide +kernel

theorem tot6826 : totK PD2M8K2 D2M8K2.t6826 = [0, 0, 238109957234, 460544010798, 159836106918, 9389920916, 0, 0] := by
  decide +kernel

theorem rows6827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6827 = true := by
  decide +kernel

theorem tot6827 : totK PD2M8K2 D2M8K2.t6827 = [0, 161596490957, 405802813252, 260106410753, 52575948615, 2463340669, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
