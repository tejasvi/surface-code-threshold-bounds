import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5696 = true := by
  decide +kernel

theorem tot5696 : totK PA10K2 A10K2.t5696 = [0, 0, 305746175225, 732523679702, 825212003191, 1471417142753, 1040409567276, 196635035010, 6239673734, 0] := by
  decide +kernel

theorem rows5697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5697 = true := by
  decide +kernel

theorem tot5697 : totK PA10K2 A10K2.t5697 = [0, 0, 465040202289, 1869049523213, 2033791473192, 561941841259, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows5698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5698 = true := by
  decide +kernel

theorem tot5698 : totK PA10K2 A10K2.t5698 = [0, 0, 0, 681286822158, 2092962783196, 1723819571005, 395323032829, 25660650750, 0, 0] := by
  decide +kernel

theorem rows5699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5699 = true := by
  decide +kernel

theorem tot5699 : totK PA10K2 A10K2.t5699 = [0, 0, 368745577193, 1555598524356, 2133808359125, 907846902077, 71257714804, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
