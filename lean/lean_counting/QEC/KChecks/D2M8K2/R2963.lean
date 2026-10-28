import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11852 = true := by
  decide +kernel

theorem tot11852 : totK PD2M8K2 D2M8K2.t11852 = [0, 55017796214, 288988479795, 369871538287, 172541512982, 19354310117, 0, 0] := by
  decide +kernel

theorem rows11853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11853 = true := by
  decide +kernel

theorem tot11853 : totK PD2M8K2 D2M8K2.t11853 = [0, 0, 211847459397, 499423144275, 192063787735, 5330797704, 0, 0] := by
  decide +kernel

theorem rows11854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11854 = true := by
  decide +kernel

theorem tot11854 : totK PD2M8K2 D2M8K2.t11854 = [0, 83682795434, 278720332566, 349951869458, 156963168011, 8077291076, 0, 0] := by
  decide +kernel

theorem rows11855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11855 = true := by
  decide +kernel

theorem tot11855 : totK PD2M8K2 D2M8K2.t11855 = [0, 180009753588, 449527392234, 263873710943, 27268577331, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
