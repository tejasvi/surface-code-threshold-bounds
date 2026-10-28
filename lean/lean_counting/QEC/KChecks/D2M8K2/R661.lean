import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2644 = true := by
  decide +kernel

theorem tot2644 : totK PD2M8K2 D2M8K2.t2644 = [0, 0, 0, 177368652858, 445242820879, 250213532375, 25191558099, 0] := by
  decide +kernel

theorem rows2645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2645 = true := by
  decide +kernel

theorem tot2645 : totK PD2M8K2 D2M8K2.t2645 = [0, 0, 0, 190948355780, 502317349538, 189297484444, 5206224793, 0] := by
  decide +kernel

theorem rows2646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2646 = true := by
  decide +kernel

theorem tot2646 : totK PD2M8K2 D2M8K2.t2646 = [0, 0, 158802970860, 383676886211, 257609796765, 90530997704, 6524090962, 0] := by
  decide +kernel

theorem rows2647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2647 = true := by
  decide +kernel

theorem tot2647 : totK PD2M8K2 D2M8K2.t2647 = [0, 0, 191631989272, 471222723544, 212565589784, 9039890340, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
