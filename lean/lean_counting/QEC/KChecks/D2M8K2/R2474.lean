import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9896 = true := by
  decide +kernel

theorem tot9896 : totK PD2M8K2 D2M8K2.t9896 = [0, 84333515894, 248780678729, 364334258164, 190274297651, 10809146906, 0, 0] := by
  decide +kernel

theorem rows9897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9897 = true := by
  decide +kernel

theorem tot9897 : totK PD2M8K2 D2M8K2.t9897 = [0, 156533364296, 455180509437, 272067730864, 26120381639, 0, 0, 0] := by
  decide +kernel

theorem rows9898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9898 = true := by
  decide +kernel

theorem tot9898 : totK PD2M8K2 D2M8K2.t9898 = [0, 140907204893, 429530122756, 297440371530, 26153733430, 0, 0, 0] := by
  decide +kernel

theorem rows9899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9899 = true := by
  decide +kernel

theorem tot9899 : totK PD2M8K2 D2M8K2.t9899 = [0, 0, 221366682972, 500194736697, 163243827035, 5398830306, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
