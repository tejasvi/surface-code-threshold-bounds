import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2568 = true := by
  decide +kernel

theorem tot2568 : totK PD2M8K2 D2M8K2.t2568 = [0, 275661885221, 504221994590, 124971418857, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows2569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2569 = true := by
  decide +kernel

theorem tot2569 : totK PD2M8K2 D2M8K2.t2569 = [0, 201545801533, 477326620855, 185230108389, 9740140984, 0, 0, 0] := by
  decide +kernel

theorem rows2570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2570 = true := by
  decide +kernel

theorem tot2570 : totK PD2M8K2 D2M8K2.t2570 = [0, 100513425366, 388538888930, 314865788643, 49388742245, 1138244013, 0, 0] := by
  decide +kernel

theorem rows2571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2571 = true := by
  decide +kernel

theorem tot2571 : totK PD2M8K2 D2M8K2.t2571 = [0, 93463593641, 381927945623, 363564718192, 44988402111, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
