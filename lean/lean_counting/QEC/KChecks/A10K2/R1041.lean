import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4164 = true := by
  decide +kernel

theorem tot4164 : totK PA10K2 A10K2.t4164 = [399361421821, 1400462784695, 1817410277809, 1011004268420, 193933203403, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4165 = true := by
  decide +kernel

theorem tot4165 : totK PA10K2 A10K2.t4165 = [152951359330, 1028088678632, 2053654702295, 1425313414289, 252253293090, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4166 = true := by
  decide +kernel

theorem tot4166 : totK PA10K2 A10K2.t4166 = [0, 571511053683, 1908236893482, 1861485884361, 550987196710, 42696891810, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4167 = true := by
  decide +kernel

theorem tot4167 : totK PA10K2 A10K2.t4167 = [0, 516189420322, 1833914665829, 1854565169327, 475940482944, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
