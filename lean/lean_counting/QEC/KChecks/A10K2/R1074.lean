import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4296 = true := by
  decide +kernel

theorem tot4296 : totK PA10K2 A10K2.t4296 = [0, 0, 42030787920, 608093953120, 1796175756481, 1649301669429, 451287104288, 30650496230, 0, 0] := by
  decide +kernel

theorem rows4297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4297 = true := by
  decide +kernel

theorem tot4297 : totK PA10K2 A10K2.t4297 = [0, 0, 515967073323, 1847895214049, 1836027986895, 468365990168, 31230200448, 0, 0, 0] := by
  decide +kernel

theorem rows4298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4298 = true := by
  decide +kernel

theorem tot4298 : totK PA10K2 A10K2.t4298 = [0, 0, 140292875551, 1292204455358, 2199354852936, 835082295920, 65326404304, 0, 0, 0] := by
  decide +kernel

theorem rows4299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4299 = true := by
  decide +kernel

theorem tot4299 : totK PA10K2 A10K2.t4299 = [0, 0, 438287101615, 1446918132209, 1793517311463, 899599497939, 153851967938, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
