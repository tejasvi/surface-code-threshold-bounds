import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5748 = true := by
  decide +kernel

theorem tot5748 : totK PD2M8K2 D2M8K2.t5748 = [0, 156627329152, 459841096351, 264468810717, 20174159953, 0, 0, 0] := by
  decide +kernel

theorem rows5749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5749 = true := by
  decide +kernel

theorem tot5749 : totK PD2M8K2 D2M8K2.t5749 = [0, 0, 234582745567, 508758893692, 135112015801, 3499003824, 0, 0] := by
  decide +kernel

theorem rows5750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5750 = true := by
  decide +kernel

theorem tot5750 : totK PD2M8K2 D2M8K2.t5750 = [0, 84228624909, 283954348745, 370005785517, 123142241953, 9484445972, 0, 0] := by
  decide +kernel

theorem rows5751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5751 = true := by
  decide +kernel

theorem tot5751 : totK PD2M8K2 D2M8K2.t5751 = [0, 155389480224, 452486104504, 272554234869, 24362870526, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
