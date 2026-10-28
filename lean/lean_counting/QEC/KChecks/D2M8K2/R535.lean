import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2140 = true := by
  decide +kernel

theorem tot2140 : totK PD2M8K2 D2M8K2.t2140 = [0, 162118832972, 459168348850, 272667171663, 28735983626, 0, 0, 0] := by
  decide +kernel

theorem rows2141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2141 = true := by
  decide +kernel

theorem tot2141 : totK PD2M8K2 D2M8K2.t2141 = [0, 0, 174244367182, 442180641711, 256434513339, 25373788367, 0, 0] := by
  decide +kernel

theorem rows2142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2142 = true := by
  decide +kernel

theorem tot2142 : totK PD2M8K2 D2M8K2.t2142 = [0, 0, 211773176040, 491536190099, 193122908450, 5430665091, 0, 0] := by
  decide +kernel

theorem rows2143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2143 = true := by
  decide +kernel

theorem tot2143 : totK PD2M8K2 D2M8K2.t2143 = [0, 156164577673, 367515928488, 265580923460, 108281992688, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
