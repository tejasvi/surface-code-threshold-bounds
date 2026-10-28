import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t268 = true := by
  decide +kernel

theorem tot268 : totK PA10K2 A10K2.t268 = [0, 0, 278536365889, 1407629495237, 2056414152445, 758965526522, 50527604982, 0, 0, 0] := by
  decide +kernel

theorem rows269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t269 = true := by
  decide +kernel

theorem tot269 : totK PA10K2 A10K2.t269 = [0, 0, 298068698356, 1222525690844, 1893136090035, 1033997914866, 160757270805, 5705019915, 0, 0] := by
  decide +kernel

theorem rows270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t270 = true := by
  decide +kernel

theorem tot270 : totK PA10K2 A10K2.t270 = [0, 0, 477824314904, 1836353719752, 2058492824438, 592235820541, 22797305663, 0, 0, 0] := by
  decide +kernel

theorem rows271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t271 = true := by
  decide +kernel

theorem tot271 : totK PA10K2 A10K2.t271 = [0, 0, 0, 770917585456, 2252567427151, 1675404281370, 291108562919, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
