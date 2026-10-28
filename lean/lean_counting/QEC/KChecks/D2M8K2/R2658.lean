import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10632 = true := by
  decide +kernel

theorem tot10632 : totK PD2M8K2 D2M8K2.t10632 = [0, 168471524745, 417621980822, 299752788606, 36127897687, 0, 0, 0] := by
  decide +kernel

theorem rows10633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10633 = true := by
  decide +kernel

theorem tot10633 : totK PD2M8K2 D2M8K2.t10633 = [0, 182145916671, 460336803442, 235732168437, 16971693599, 0, 0, 0] := by
  decide +kernel

theorem rows10634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10634 = true := by
  decide +kernel

theorem tot10634 : totK PD2M8K2 D2M8K2.t10634 = [0, 68188677921, 363174304185, 370981408827, 98757501388, 13135967731, 0, 0] := by
  decide +kernel

theorem rows10635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10635 = true := by
  decide +kernel

theorem tot10635 : totK PD2M8K2 D2M8K2.t10635 = [0, 0, 171810180533, 457950870962, 244917600364, 14866273106, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
