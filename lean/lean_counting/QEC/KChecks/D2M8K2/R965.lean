import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3860 = true := by
  decide +kernel

theorem tot3860 : totK PD2M8K2 D2M8K2.t3860 = [0, 155109350687, 447335405256, 270508147192, 20903619224, 0, 0, 0] := by
  decide +kernel

theorem rows3861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3861 = true := by
  decide +kernel

theorem tot3861 : totK PD2M8K2 D2M8K2.t3861 = [0, 0, 226854532431, 479795075609, 141904175642, 4931404646, 0, 0] := by
  decide +kernel

theorem rows3862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3862 = true := by
  decide +kernel

theorem tot3862 : totK PD2M8K2 D2M8K2.t3862 = [0, 142341435800, 443238243854, 283065960101, 26079763371, 0, 0, 0] := by
  decide +kernel

theorem rows3863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3863 = true := by
  decide +kernel

theorem tot3863 : totK PD2M8K2 D2M8K2.t3863 = [0, 176737685543, 451181751070, 268649730264, 25022329187, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
