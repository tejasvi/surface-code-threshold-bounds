import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1408 = true := by
  decide +kernel

theorem tot1408 : totK PA10K2 A10K2.t1408 = [0, 0, 0, 0, 201061290646, 1442736283320, 2069609268571, 702720348025, 44949217999, 0] := by
  decide +kernel

theorem rows1409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1409 = true := by
  decide +kernel

theorem tot1409 : totK PA10K2 A10K2.t1409 = [0, 0, 0, 0, 361824646052, 1292864947952, 1826230223242, 936186057456, 157528949620, 5528811039] := by
  decide +kernel

theorem rows1410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1410 = true := by
  decide +kernel

theorem tot1410 : totK PA10K2 A10K2.t1410 = [0, 0, 0, 306117011728, 1219903811633, 1804466610985, 1233982219358, 340634440597, 29010686974, 0] := by
  decide +kernel

theorem rows1411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1411 = true := by
  decide +kernel

theorem tot1411 : totK PA10K2 A10K2.t1411 = [0, 0, 0, 488554552263, 1793799858872, 1936414664180, 536831172632, 32040661968, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
