import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6088 = true := by
  decide +kernel

theorem tot6088 : totK PA10K2 A10K2.t6088 = [0, 0, 399915152979, 1741064651565, 2139158436378, 724267144501, 55647277921, 0, 0, 0] := by
  decide +kernel

theorem rows6089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6089 = true := by
  decide +kernel

theorem tot6089 : totK PA10K2 A10K2.t6089 = [0, 0, 127288525858, 937090138467, 2091600619540, 1448684789642, 253965913742, 7151180950, 0, 0] := by
  decide +kernel

theorem rows6090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6090 = true := by
  decide +kernel

theorem tot6090 : totK PA10K2 A10K2.t6090 = [0, 0, 575978637024, 1999377496282, 2017434673243, 523494689313, 18515547658, 0, 0, 0] := by
  decide +kernel

theorem rows6091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6091 = true := by
  decide +kernel

theorem tot6091 : totK PA10K2 A10K2.t6091 = [0, 300827602965, 1070908883296, 1568006710956, 1426648849850, 561716472710, 50432252117, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
