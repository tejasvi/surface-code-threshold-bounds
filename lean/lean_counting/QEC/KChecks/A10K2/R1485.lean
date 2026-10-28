import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5940 = true := by
  decide +kernel

theorem tot5940 : totK PA10K2 A10K2.t5940 = [0, 515154299475, 1911799866049, 2030544090362, 571451830541, 23385739874, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5941 = true := by
  decide +kernel

theorem tot5941 : totK PA10K2 A10K2.t5941 = [0, 218754815241, 1353179925556, 2179060135063, 1099102350258, 113389045580, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5942 = true := by
  decide +kernel

theorem tot5942 : totK PA10K2 A10K2.t5942 = [0, 0, 551649133869, 2022885428407, 1982945329289, 409560548686, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows5943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5943 = true := by
  decide +kernel

theorem tot5943 : totK PA10K2 A10K2.t5943 = [0, 427178422353, 1387900558918, 1554106858989, 1042912761373, 469588624515, 48886019071, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
