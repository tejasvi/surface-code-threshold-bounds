import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5996 = true := by
  decide +kernel

theorem tot5996 : totK PD2M8K2 D2M8K2.t5996 = [0, 166181834610, 466176653897, 245054015908, 15237169554, 0, 0, 0] := by
  decide +kernel

theorem rows5997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5997 = true := by
  decide +kernel

theorem tot5997 : totK PD2M8K2 D2M8K2.t5997 = [0, 0, 281679095470, 509486469895, 93748988858, 1275377855, 0, 0] := by
  decide +kernel

theorem rows5998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5998 = true := by
  decide +kernel

theorem tot5998 : totK PD2M8K2 D2M8K2.t5998 = [0, 183106467492, 436866446373, 281085169596, 34750256832, 0, 0, 0] := by
  decide +kernel

theorem rows5999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5999 = true := by
  decide +kernel

theorem tot5999 : totK PD2M8K2 D2M8K2.t5999 = [0, 159217209691, 471132710982, 248412583560, 15794999357, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
