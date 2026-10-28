import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8100 = true := by
  decide +kernel

theorem tot8100 : totK PD2M8K2 D2M8K2.t8100 = [0, 0, 0, 170988281537, 444367999159, 252336184322, 23659519022, 0] := by
  decide +kernel

theorem rows8101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8101 = true := by
  decide +kernel

theorem tot8101 : totK PD2M8K2 D2M8K2.t8101 = [0, 0, 0, 168954878601, 483638520288, 221656730957, 7248992294, 0] := by
  decide +kernel

theorem rows8102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8102 = true := by
  decide +kernel

theorem tot8102 : totK PD2M8K2 D2M8K2.t8102 = [0, 0, 193448620848, 459035098294, 239460272972, 22859916867, 2106824728, 0] := by
  decide +kernel

theorem rows8103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8103 = true := by
  decide +kernel

theorem tot8103 : totK PD2M8K2 D2M8K2.t8103 = [0, 0, 199733194784, 474716952211, 213201431892, 12279160303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
