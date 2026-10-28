import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t748 = true := by
  decide +kernel

theorem tot748 : totK PA10K2 A10K2.t748 = [0, 0, 972914611455, 2399036096988, 1141166738933, 104302380178, 0, 0, 0, 0] := by
  decide +kernel

theorem rows749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t749 = true := by
  decide +kernel

theorem tot749 : totK PA10K2 A10K2.t749 = [496869944875, 1598479797272, 1446868059503, 624214490554, 483598834124, 161470909364, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t750 = true := by
  decide +kernel

theorem tot750 : totK PA10K2 A10K2.t750 = [304479794002, 1527501647385, 2177447732623, 906052283907, 78055416248, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t751 = true := by
  decide +kernel

theorem tot751 : totK PA10K2 A10K2.t751 = [0, 541162459470, 1952852299415, 1836816719225, 481087119594, 30810868011, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
