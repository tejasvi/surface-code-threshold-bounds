import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10712 = true := by
  decide +kernel

theorem tot10712 : totK PD2M8K2 D2M8K2.t10712 = [0, 0, 159767150191, 471216880347, 254833621914, 13632511348, 0, 0] := by
  decide +kernel

theorem rows10713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10713 = true := by
  decide +kernel

theorem tot10713 : totK PD2M8K2 D2M8K2.t10713 = [0, 0, 0, 302881902852, 497900477591, 81316071731, 1164319620, 0] := by
  decide +kernel

theorem rows10714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10714 = true := by
  decide +kernel

theorem tot10714 : totK PD2M8K2 D2M8K2.t10714 = [0, 0, 102798101328, 361288735615, 320473954347, 77836154758, 3462014130, 0] := by
  decide +kernel

theorem rows10715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10715 = true := by
  decide +kernel

theorem tot10715 : totK PD2M8K2 D2M8K2.t10715 = [0, 0, 188276338548, 453958048726, 247757376231, 19843026077, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
