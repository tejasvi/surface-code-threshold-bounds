import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2968 = true := by
  decide +kernel

theorem tot2968 : totK PD2M8K2 D2M8K2.t2968 = [0, 189878316679, 455604094944, 226301398083, 16995378214, 0, 0, 0] := by
  decide +kernel

theorem rows2969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2969 = true := by
  decide +kernel

theorem tot2969 : totK PD2M8K2 D2M8K2.t2969 = [0, 105163496704, 423155273610, 325539397595, 31186575412, 0, 0, 0] := by
  decide +kernel

theorem rows2970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2970 = true := by
  decide +kernel

theorem tot2970 : totK PD2M8K2 D2M8K2.t2970 = [0, 0, 273411054123, 506919348819, 108661779997, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2971 = true := by
  decide +kernel

theorem tot2971 : totK PD2M8K2 D2M8K2.t2971 = [0, 159897023672, 451418386760, 275798194392, 27766257782, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
