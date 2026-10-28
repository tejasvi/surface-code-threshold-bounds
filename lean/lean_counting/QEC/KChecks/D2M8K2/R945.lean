import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3780 = true := by
  decide +kernel

theorem tot3780 : totK PD2M8K2 D2M8K2.t3780 = [0, 0, 302380279965, 474328789847, 83072397649, 1206465782, 0, 0] := by
  decide +kernel

theorem rows3781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3781 = true := by
  decide +kernel

theorem tot3781 : totK PD2M8K2 D2M8K2.t3781 = [0, 181896194215, 455344112958, 265457819013, 28140143540, 0, 0, 0] := by
  decide +kernel

theorem rows3782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3782 = true := by
  decide +kernel

theorem tot3782 : totK PD2M8K2 D2M8K2.t3782 = [0, 197713887829, 481649120905, 223840291264, 10752121309, 0, 0, 0] := by
  decide +kernel

theorem rows3783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3783 = true := by
  decide +kernel

theorem tot3783 : totK PD2M8K2 D2M8K2.t3783 = [0, 190853236419, 469968256359, 216936606254, 12835581599, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
