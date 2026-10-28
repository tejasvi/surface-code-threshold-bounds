import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1236 = true := by
  decide +kernel

theorem tot1236 : totK PD2M8K2 D2M8K2.t1236 = [0, 156136406509, 437445620087, 295329992558, 30941577571, 0, 0, 0] := by
  decide +kernel

theorem rows1237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1237 = true := by
  decide +kernel

theorem tot1237 : totK PD2M8K2 D2M8K2.t1237 = [0, 200772432011, 462640164799, 219428001901, 14483116170, 0, 0, 0] := by
  decide +kernel

theorem rows1238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1238 = true := by
  decide +kernel

theorem tot1238 : totK PD2M8K2 D2M8K2.t1238 = [0, 45816874822, 389329177815, 420221632748, 55383342071, 0, 0, 0] := by
  decide +kernel

theorem rows1239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1239 = true := by
  decide +kernel

theorem tot1239 : totK PD2M8K2 D2M8K2.t1239 = [0, 52304417024, 237877550461, 427668093582, 155597560515, 5218872685, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
