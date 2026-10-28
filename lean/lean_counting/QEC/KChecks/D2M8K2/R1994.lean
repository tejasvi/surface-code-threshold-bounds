import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7976 = true := by
  decide +kernel

theorem tot7976 : totK PD2M8K2 D2M8K2.t7976 = [0, 0, 113177815050, 442522540823, 319563199956, 30036783765, 0, 0] := by
  decide +kernel

theorem rows7977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7977 = true := by
  decide +kernel

theorem tot7977 : totK PD2M8K2 D2M8K2.t7977 = [0, 0, 0, 245462563358, 511311760982, 136814057243, 7273823680, 0] := by
  decide +kernel

theorem rows7978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7978 = true := by
  decide +kernel

theorem tot7978 : totK PD2M8K2 D2M8K2.t7978 = [0, 0, 156602297117, 378123191419, 313182507827, 63720666467, 2478123692, 0] := by
  decide +kernel

theorem rows7979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7979 = true := by
  decide +kernel

theorem tot7979 : totK PD2M8K2 D2M8K2.t7979 = [0, 0, 207396097259, 494583232819, 202180334650, 11384824706, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
