import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6144 = true := by
  decide +kernel

theorem tot6144 : totK PA10K2 A10K2.t6144 = [0, 0, 301694793695, 1418679546337, 2149589791445, 1030987299934, 90823748878, 0, 0, 0] := by
  decide +kernel

theorem rows6145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6145 = true := by
  decide +kernel

theorem tot6145 : totK PA10K2 A10K2.t6145 = [0, 0, 216509039614, 1144122905672, 2073797916174, 1271164776827, 227515621588, 6904928264, 0, 0] := by
  decide +kernel

theorem rows6146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6146 = true := by
  decide +kernel

theorem tot6146 : totK PA10K2 A10K2.t6146 = [0, 0, 582726840359, 1852104593930, 1909875345136, 704692116302, 57657992128, 0, 0, 0] := by
  decide +kernel

theorem rows6147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6147 = true := by
  decide +kernel

theorem tot6147 : totK PA10K2 A10K2.t6147 = [0, 0, 472903741962, 1864277507442, 2075746589400, 543349958987, 18698036191, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
