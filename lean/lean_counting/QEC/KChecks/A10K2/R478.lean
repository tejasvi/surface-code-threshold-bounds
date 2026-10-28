import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1912 = true := by
  decide +kernel

theorem tot1912 : totK PA10K2 A10K2.t1912 = [0, 253046812372, 1219771493434, 2026391877530, 1246073358164, 205029729344, 6032141194, 0, 0, 0] := by
  decide +kernel

theorem rows1913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1913 = true := by
  decide +kernel

theorem tot1913 : totK PA10K2 A10K2.t1913 = [0, 613900238201, 1913964271322, 1845533175725, 560117542131, 42292542925, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1914 = true := by
  decide +kernel

theorem tot1914 : totK PA10K2 A10K2.t1914 = [0, 0, 840729042969, 2243430762904, 1605639459170, 288264112873, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows1915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1915 = true := by
  decide +kernel

theorem tot1915 : totK PA10K2 A10K2.t1915 = [0, 0, 500766308723, 1926307908451, 2055152218128, 543983394313, 18818953403, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
