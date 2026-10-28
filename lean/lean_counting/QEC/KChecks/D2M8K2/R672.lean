import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2688 = true := by
  decide +kernel

theorem tot2688 : totK PD2M8K2 D2M8K2.t2688 = [0, 0, 0, 222663075830, 474772394578, 156411320487, 5320761635, 0] := by
  decide +kernel

theorem rows2689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2689 = true := by
  decide +kernel

theorem tot2689 : totK PD2M8K2 D2M8K2.t2689 = [0, 0, 198096895259, 459087029030, 215753856578, 16131077680, 0, 0] := by
  decide +kernel

theorem rows2690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2690 = true := by
  decide +kernel

theorem tot2690 : totK PD2M8K2 D2M8K2.t2690 = [0, 0, 210403521034, 478358816691, 195004811640, 9721971944, 0, 0] := by
  decide +kernel

theorem rows2691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2691 = true := by
  decide +kernel

theorem tot2691 : totK PD2M8K2 D2M8K2.t2691 = [0, 0, 0, 404084021614, 427445150504, 38360905369, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
