import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2704 = true := by
  decide +kernel

theorem tot2704 : totK PA10K2 A10K2.t2704 = [0, 0, 281061589004, 1545454843097, 2141828045945, 684857438802, 39194129615, 0, 0, 0] := by
  decide +kernel

theorem rows2705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2705 = true := by
  decide +kernel

theorem tot2705 : totK PA10K2 A10K2.t2705 = [0, 0, 264190058193, 1233733258318, 1934324444554, 1060490694477, 174361211873, 5546304973, 0, 0] := by
  decide +kernel

theorem rows2706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2706 = true := by
  decide +kernel

theorem tot2706 : totK PA10K2 A10K2.t2706 = [0, 581438935932, 1914273447339, 1784058290136, 503756549935, 44915948549, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2707 = true := by
  decide +kernel

theorem tot2707 : totK PA10K2 A10K2.t2707 = [0, 232932240082, 1379111259586, 2246025618426, 971981550757, 76300810480, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
