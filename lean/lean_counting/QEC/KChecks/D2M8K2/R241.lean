import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t964 = true := by
  decide +kernel

theorem tot964 : totK PD2M8K2 D2M8K2.t964 = [0, 175196365373, 486191365131, 219676251573, 7992090037, 0, 0, 0] := by
  decide +kernel

theorem rows965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t965 = true := by
  decide +kernel

theorem tot965 : totK PD2M8K2 D2M8K2.t965 = [137802269863, 362146138126, 285572960582, 113939855773, 6975219520, 0, 0, 0] := by
  decide +kernel

theorem rows966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t966 = true := by
  decide +kernel

theorem tot966 : totK PD2M8K2 D2M8K2.t966 = [164822517489, 440158051985, 278160490174, 29568678322, 0, 0, 0, 0] := by
  decide +kernel

theorem rows967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t967 = true := by
  decide +kernel

theorem tot967 : totK PD2M8K2 D2M8K2.t967 = [131649220673, 444485065936, 300120284783, 23361826984, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
