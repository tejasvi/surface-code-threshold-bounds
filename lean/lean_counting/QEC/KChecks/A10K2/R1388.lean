import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5552 = true := by
  decide +kernel

theorem tot5552 : totK PA10K2 A10K2.t5552 = [0, 0, 0, 524869949689, 1914105139306, 1937259672184, 482694649478, 18064666500, 0, 0] := by
  decide +kernel

theorem rows5553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5553 = true := by
  decide +kernel

theorem tot5553 : totK PA10K2 A10K2.t5553 = [0, 0, 0, 0, 773466462228, 2216244522352, 1528552275088, 265789490416, 7151180950, 0] := by
  decide +kernel

theorem rows5554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5554 = true := by
  decide +kernel

theorem tot5554 : totK PA10K2 A10K2.t5554 = [0, 0, 0, 749282172628, 2079925210802, 1621059905436, 383232056201, 30107499662, 0, 0] := by
  decide +kernel

theorem rows5555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5555 = true := by
  decide +kernel

theorem tot5555 : totK PA10K2 A10K2.t5555 = [0, 0, 0, 609181556495, 2161055158621, 1927576096288, 414797246744, 12199886344, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
