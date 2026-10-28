import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15132 = true := by
  decide +kernel

theorem tot15132 : totK PD2M8K2 D2M8K2.t15132 = [0, 104904165133, 326338504848, 320657979714, 143270595761, 13566920432, 0, 0] := by
  decide +kernel

theorem rows15133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15133 = true := by
  decide +kernel

theorem tot15133 : totK PD2M8K2 D2M8K2.t15133 = [0, 186750105439, 457501924654, 225981214361, 17111997474, 0, 0, 0] := by
  decide +kernel

theorem rows15134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15134 = true := by
  decide +kernel

theorem tot15134 : totK PD2M8K2 D2M8K2.t15134 = [0, 123641764684, 430701398959, 306873176741, 28492415024, 0, 0, 0] := by
  decide +kernel

theorem rows15135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15135 = true := by
  decide +kernel

theorem tot15135 : totK PD2M8K2 D2M8K2.t15135 = [0, 0, 272164921570, 505847044851, 110355431096, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
