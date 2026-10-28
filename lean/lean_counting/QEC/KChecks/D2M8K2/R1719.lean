import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6876 = true := by
  decide +kernel

theorem tot6876 : totK PD2M8K2 D2M8K2.t6876 = [53441125967, 325704736727, 427487525729, 93301987935, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows6877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6877 = true := by
  decide +kernel

theorem tot6877 : totK PD2M8K2 D2M8K2.t6877 = [0, 210721316225, 478369907223, 175005733507, 9373855646, 0, 0, 0] := by
  decide +kernel

theorem rows6878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6878 = true := by
  decide +kernel

theorem tot6878 : totK PD2M8K2 D2M8K2.t6878 = [177205241102, 463615530569, 261816503150, 29608135791, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6879 = true := by
  decide +kernel

theorem tot6879 : totK PD2M8K2 D2M8K2.t6879 = [176488303782, 459562557503, 256249490656, 19876515391, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
