import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2156 = true := by
  decide +kernel

theorem tot2156 : totK PA10K2 A10K2.t2156 = [0, 583381828075, 1881619281591, 1791146251501, 517125444752, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2157 = true := by
  decide +kernel

theorem tot2157 : totK PA10K2 A10K2.t2157 = [0, 0, 1013749993189, 2399226218858, 1181479206266, 106330077380, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2158 = true := by
  decide +kernel

theorem tot2158 : totK PA10K2 A10K2.t2158 = [0, 474944754325, 1505451236575, 1752726965731, 985973589105, 194271170553, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2159 = true := by
  decide +kernel

theorem tot2159 : totK PA10K2 A10K2.t2159 = [0, 117338935714, 970488940199, 2181582964713, 1518550478401, 247403788496, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
