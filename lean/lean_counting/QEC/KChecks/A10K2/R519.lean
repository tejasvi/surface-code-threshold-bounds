import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2076 = true := by
  decide +kernel

theorem tot2076 : totK PA10K2 A10K2.t2076 = [0, 44718331091, 822356761061, 2108066859944, 1566001374740, 363272824737, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2077 = true := by
  decide +kernel

theorem tot2077 : totK PA10K2 A10K2.t2077 = [0, 146952719065, 911263458411, 1919709417624, 1472552470184, 257415765184, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2078 = true := by
  decide +kernel

theorem tot2078 : totK PA10K2 A10K2.t2078 = [0, 535566673136, 1761898117200, 1862860454261, 547438632359, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2079 = true := by
  decide +kernel

theorem tot2079 : totK PA10K2 A10K2.t2079 = [0, 39815911663, 1126502732886, 2305569493805, 1062515936003, 77889413895, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
