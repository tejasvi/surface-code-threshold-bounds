import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5256 = true := by
  decide +kernel

theorem tot5256 : totK PA10K2 A10K2.t5256 = [0, 476589019535, 1728580547631, 1842755186233, 674837386403, 74144978812, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5257 = true := by
  decide +kernel

theorem tot5257 : totK PA10K2 A10K2.t5257 = [0, 293434943870, 1440916566590, 2134424760080, 849682591531, 61340920068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5258 = true := by
  decide +kernel

theorem tot5258 : totK PA10K2 A10K2.t5258 = [0, 293349203532, 1214727573051, 1849664214099, 1162958516479, 220083983484, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5259 = true := by
  decide +kernel

theorem tot5259 : totK PA10K2 A10K2.t5259 = [0, 258963577619, 1390319160097, 2209083489446, 984921466803, 82844588672, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
