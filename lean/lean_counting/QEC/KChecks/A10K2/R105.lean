import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t420 = true := by
  decide +kernel

theorem tot420 : totK PA10K2 A10K2.t420 = [0, 515769748030, 1774650595472, 1934078156980, 619990905719, 39266247089, 0, 0, 0, 0] := by
  decide +kernel

theorem rows421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t421 = true := by
  decide +kernel

theorem tot421 : totK PA10K2 A10K2.t421 = [0, 479766724473, 1817827236385, 1888769275179, 479241402840, 31088438951, 0, 0, 0, 0] := by
  decide +kernel

theorem rows422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t422 = true := by
  decide +kernel

theorem tot422 : totK PA10K2 A10K2.t422 = [0, 529963201293, 1850097676274, 1738414687811, 409337177601, 25533540376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t423 = true := by
  decide +kernel

theorem tot423 : totK PA10K2 A10K2.t423 = [0, 0, 889860391308, 2329952014857, 1223162657191, 124864262566, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
