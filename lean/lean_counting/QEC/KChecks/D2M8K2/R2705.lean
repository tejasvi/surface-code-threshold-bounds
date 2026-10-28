import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10820 = true := by
  decide +kernel

theorem tot10820 : totK PD2M8K2 D2M8K2.t10820 = [0, 0, 174826212511, 454950463483, 270363428718, 17074208338, 0, 0] := by
  decide +kernel

theorem rows10821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10821 = true := by
  decide +kernel

theorem tot10821 : totK PD2M8K2 D2M8K2.t10821 = [0, 0, 172849268966, 465999423105, 256114124826, 13336485982, 0, 0] := by
  decide +kernel

theorem rows10822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10822 = true := by
  decide +kernel

theorem tot10822 : totK PD2M8K2 D2M8K2.t10822 = [0, 0, 0, 193200862053, 456102185624, 231313487389, 21361625106, 0] := by
  decide +kernel

theorem rows10823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10823 = true := by
  decide +kernel

theorem tot10823 : totK PD2M8K2 D2M8K2.t10823 = [0, 0, 0, 218810228328, 487601946059, 180698743975, 5206224793, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
