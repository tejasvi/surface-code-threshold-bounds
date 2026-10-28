import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5408 = true := by
  decide +kernel

theorem tot5408 : totK PA10K2 A10K2.t5408 = [0, 0, 227410598617, 1231491233556, 2140992141492, 1257234921868, 161243704444, 0, 0, 0] := by
  decide +kernel

theorem rows5409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5409 = true := by
  decide +kernel

theorem tot5409 : totK PA10K2 A10K2.t5409 = [0, 0, 261343918786, 1287503629279, 2163495701811, 1183799615309, 150907032003, 7047025452, 0, 0] := by
  decide +kernel

theorem rows5410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5410 = true := by
  decide +kernel

theorem tot5410 : totK PA10K2 A10K2.t5410 = [0, 0, 537368149671, 1936125410372, 1918760354204, 512333657615, 18513647723, 0, 0, 0] := by
  decide +kernel

theorem rows5411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5411 = true := by
  decide +kernel

theorem tot5411 : totK PA10K2 A10K2.t5411 = [0, 0, 0, 677879107642, 2242830338071, 1881459447432, 305916049533, 6157148557, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
