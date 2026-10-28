import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5436 = true := by
  decide +kernel

theorem tot5436 : totK PD2M8K2 D2M8K2.t5436 = [0, 0, 0, 122082854229, 456662117608, 280285949353, 21919970102, 0] := by
  decide +kernel

theorem rows5437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5437 = true := by
  decide +kernel

theorem tot5437 : totK PD2M8K2 D2M8K2.t5437 = [0, 0, 0, 14084561518, 314211514351, 454933424869, 89856978661, 1501162176] := by
  decide +kernel

theorem rows5438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5438 = true := by
  decide +kernel

theorem tot5438 : totK PD2M8K2 D2M8K2.t5438 = [0, 0, 0, 294596849464, 481469742494, 105850555376, 1262285478, 0] := by
  decide +kernel

theorem rows5439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5439 = true := by
  decide +kernel

theorem tot5439 : totK PD2M8K2 D2M8K2.t5439 = [0, 0, 0, 178641363101, 492288364474, 202885578670, 9896803301, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
