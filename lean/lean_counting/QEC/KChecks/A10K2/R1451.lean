import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5804 = true := by
  decide +kernel

theorem tot5804 : totK PA10K2 A10K2.t5804 = [0, 0, 496116447412, 1759469836488, 1893023268921, 566046314357, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows5805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5805 = true := by
  decide +kernel

theorem tot5805 : totK PA10K2 A10K2.t5805 = [0, 0, 31645740394, 756456124005, 2047503604703, 1612087387003, 374955275659, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5806 = true := by
  decide +kernel

theorem tot5806 : totK PA10K2 A10K2.t5806 = [0, 0, 165545589068, 972078838631, 1921394686242, 1380272911105, 236119922122, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5807 = true := by
  decide +kernel

theorem tot5807 : totK PA10K2 A10K2.t5807 = [0, 0, 483557930266, 1682035889978, 1892487403349, 646975091536, 51788092923, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
