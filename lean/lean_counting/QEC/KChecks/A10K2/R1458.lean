import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5832 = true := by
  decide +kernel

theorem tot5832 : totK PA10K2 A10K2.t5832 = [0, 0, 0, 755700817057, 2146227104376, 1649988941558, 379981594513, 25715051306, 0, 0] := by
  decide +kernel

theorem rows5833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5833 = true := by
  decide +kernel

theorem tot5833 : totK PA10K2 A10K2.t5833 = [0, 0, 287800699719, 1240974426641, 1960663270481, 1262136591434, 216657779258, 5807182206, 0, 0] := by
  decide +kernel

theorem rows5834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5834 = true := by
  decide +kernel

theorem tot5834 : totK PA10K2 A10K2.t5834 = [0, 0, 307423764049, 1482578091128, 2243513555519, 966397749501, 71822882984, 0, 0, 0] := by
  decide +kernel

theorem rows5835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5835 = true := by
  decide +kernel

theorem tot5835 : totK PA10K2 A10K2.t5835 = [0, 0, 307367748945, 1236403968309, 1916427660906, 1337759764782, 257605848008, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
