import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5268 = true := by
  decide +kernel

theorem tot5268 : totK PA10K2 A10K2.t5268 = [0, 459928825582, 1845604988054, 2060928932475, 551920092052, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5269 = true := by
  decide +kernel

theorem tot5269 : totK PA10K2 A10K2.t5269 = [0, 0, 571258711512, 2049741551850, 1770133493259, 362459895093, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5270 = true := by
  decide +kernel

theorem tot5270 : totK PA10K2 A10K2.t5270 = [0, 482075982605, 1598973477904, 1776209545280, 848882145360, 150345041223, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5271 = true := by
  decide +kernel

theorem tot5271 : totK PA10K2 A10K2.t5271 = [0, 297317356254, 1569116821805, 2152083610543, 729101133453, 53383554103, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
