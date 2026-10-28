import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t940 = true := by
  decide +kernel

theorem tot940 : totK PD2M8K2 D2M8K2.t940 = [0, 288043565612, 513664100718, 105936821339, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t941 = true := by
  decide +kernel

theorem tot941 : totK PD2M8K2 D2M8K2.t941 = [0, 198091919949, 476274001401, 219665069371, 20098128356, 0, 0, 0] := by
  decide +kernel

theorem rows942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t942 = true := by
  decide +kernel

theorem tot942 : totK PD2M8K2 D2M8K2.t942 = [0, 173644233338, 445531192855, 264092026351, 17364379615, 0, 0, 0] := by
  decide +kernel

theorem rows943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t943 = true := by
  decide +kernel

theorem tot943 : totK PD2M8K2 D2M8K2.t943 = [0, 161718535257, 467194083647, 266496915444, 23978581832, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
