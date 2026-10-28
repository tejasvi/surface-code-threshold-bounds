import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7772 = true := by
  decide +kernel

theorem tot7772 : totK PA10K2 A10K2.t7772 = [0, 0, 0, 704732909775, 2102094580121, 1612536665266, 374388583071, 25239774317, 0, 0] := by
  decide +kernel

theorem rows7773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7773 = true := by
  decide +kernel

theorem tot7773 : totK PA10K2 A10K2.t7773 = [0, 0, 286854300018, 1283972716898, 1862007842930, 1011632301404, 169942575727, 5410721913, 0, 0] := by
  decide +kernel

theorem rows7774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7774 = true := by
  decide +kernel

theorem tot7774 : totK PA10K2 A10K2.t7774 = [0, 0, 293457878574, 1466144789778, 2052095470424, 737491935570, 58581722383, 0, 0, 0] := by
  decide +kernel

theorem rows7775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7775 = true := by
  decide +kernel

theorem tot7775 : totK PA10K2 A10K2.t7775 = [0, 0, 296268317924, 1288913265278, 1931336622276, 1015059400427, 174248308392, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
