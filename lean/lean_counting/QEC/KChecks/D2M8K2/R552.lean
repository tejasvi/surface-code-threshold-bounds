import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2208 = true := by
  decide +kernel

theorem tot2208 : totK PD2M8K2 D2M8K2.t2208 = [0, 179321109299, 466760547890, 250416061815, 22444158425, 0, 0, 0] := by
  decide +kernel

theorem rows2209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2209 = true := by
  decide +kernel

theorem tot2209 : totK PD2M8K2 D2M8K2.t2209 = [0, 188960930031, 477006713969, 226301570809, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows2210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2210 = true := by
  decide +kernel

theorem tot2210 : totK PD2M8K2 D2M8K2.t2210 = [0, 19233732584, 302587253485, 465506546827, 100268622889, 1198073392, 0, 0] := by
  decide +kernel

theorem rows2211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2211 = true := by
  decide +kernel

theorem tot2211 : totK PD2M8K2 D2M8K2.t2211 = [0, 0, 196697382114, 477608184153, 195028465260, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
