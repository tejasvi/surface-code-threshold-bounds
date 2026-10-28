import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5256 = true := by
  decide +kernel

theorem tot5256 : totK PD2M8K2 D2M8K2.t5256 = [0, 0, 206189362182, 490337832886, 219522087020, 8930464173, 0, 0] := by
  decide +kernel

theorem rows5257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5257 = true := by
  decide +kernel

theorem tot5257 : totK PD2M8K2 D2M8K2.t5257 = [0, 0, 55790968923, 287107514510, 374321144386, 174539432771, 21385604922, 0] := by
  decide +kernel

theorem rows5258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5258 = true := by
  decide +kernel

theorem tot5258 : totK PD2M8K2 D2M8K2.t5258 = [0, 0, 0, 207821445132, 483472103858, 192867044259, 7658844075, 0] := by
  decide +kernel

theorem rows5259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5259 = true := by
  decide +kernel

theorem tot5259 : totK PD2M8K2 D2M8K2.t5259 = [0, 0, 65839548356, 241663385337, 391150078466, 172950270394, 7877424857, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
