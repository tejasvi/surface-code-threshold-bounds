import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2264 = true := by
  decide +kernel

theorem tot2264 : totK PA10K2 A10K2.t2264 = [0, 0, 259898496209, 1180572209927, 1860214448331, 1124746095083, 184948989179, 5517381808, 0, 0] := by
  decide +kernel

theorem rows2265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2265 = true := by
  decide +kernel

theorem tot2265 : totK PA10K2 A10K2.t2265 = [0, 0, 459707760380, 1818429501923, 1926157560428, 472721368785, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows2266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2266 = true := by
  decide +kernel

theorem tot2266 : totK PA10K2 A10K2.t2266 = [0, 0, 0, 714148898387, 2216299319339, 1397778241879, 136342356832, 0, 0, 0] := by
  decide +kernel

theorem rows2267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2267 = true := by
  decide +kernel

theorem tot2267 : totK PA10K2 A10K2.t2267 = [0, 0, 556560574152, 1890335796195, 1885969065594, 587293131299, 102252252735, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
