import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7084 = true := by
  decide +kernel

theorem tot7084 : totK PA10K2 A10K2.t7084 = [0, 0, 0, 571604056622, 2005492293560, 1944974674372, 411840495424, 11924387614, 0, 0] := by
  decide +kernel

theorem rows7085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7085 = true := by
  decide +kernel

theorem tot7085 : totK PA10K2 A10K2.t7085 = [0, 0, 0, 0, 844511172606, 2262226679640, 1509646670928, 225747759638, 6439430839, 0] := by
  decide +kernel

theorem rows7086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7086 = true := by
  decide +kernel

theorem tot7086 : totK PA10K2 A10K2.t7086 = [0, 0, 0, 550113062824, 1820565235330, 1810350932472, 643040182069, 60790496763, 0, 0] := by
  decide +kernel

theorem rows7087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7087 = true := by
  decide +kernel

theorem tot7087 : totK PA10K2 A10K2.t7087 = [0, 0, 0, 328627686157, 1549966163555, 2172423962464, 836381716815, 62210555275, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
