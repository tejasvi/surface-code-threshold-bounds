import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5952 = true := by
  decide +kernel

theorem tot5952 : totK PD2M8K2 D2M8K2.t5952 = [0, 0, 254117924817, 489915043812, 132469334287, 2243379097, 0, 0] := by
  decide +kernel

theorem rows5953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5953 = true := by
  decide +kernel

theorem tot5953 : totK PD2M8K2 D2M8K2.t5953 = [0, 0, 175398204684, 455263943165, 211651029221, 12430730167, 0, 0] := by
  decide +kernel

theorem rows5954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5954 = true := by
  decide +kernel

theorem tot5954 : totK PD2M8K2 D2M8K2.t5954 = [0, 183285179032, 435626500958, 260956580889, 49540188655, 7077058802, 0, 0] := by
  decide +kernel

theorem rows5955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5955 = true := by
  decide +kernel

theorem tot5955 : totK PD2M8K2 D2M8K2.t5955 = [0, 176496611913, 487164069717, 233247179634, 10879400989, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
