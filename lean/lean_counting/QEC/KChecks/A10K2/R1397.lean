import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5588 = true := by
  decide +kernel

theorem tot5588 : totK PA10K2 A10K2.t5588 = [0, 0, 550113440656, 1946294438065, 1876595707007, 433795696278, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows5589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5589 = true := by
  decide +kernel

theorem tot5589 : totK PA10K2 A10K2.t5589 = [0, 0, 454000514958, 1746251683821, 1942024711415, 553384930698, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows5590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5590 = true := by
  decide +kernel

theorem tot5590 : totK PA10K2 A10K2.t5590 = [0, 0, 465830899204, 1729409979989, 1884401845550, 560681902921, 50267370225, 0, 0, 0] := by
  decide +kernel

theorem rows5591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5591 = true := by
  decide +kernel

theorem tot5591 : totK PA10K2 A10K2.t5591 = [0, 0, 204438867854, 1401792067251, 2182926191649, 793810575447, 58503570348, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
