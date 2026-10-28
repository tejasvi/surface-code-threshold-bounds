import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11616 = true := by
  decide +kernel

theorem tot11616 : totK PD2M8K2 D2M8K2.t11616 = [0, 194524833362, 469856857503, 221605477936, 12320791933, 0, 0, 0] := by
  decide +kernel

theorem rows11617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11617 = true := by
  decide +kernel

theorem tot11617 : totK PD2M8K2 D2M8K2.t11617 = [0, 32584286286, 379231946743, 437380961821, 53634586475, 0, 0, 0] := by
  decide +kernel

theorem rows11618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11618 = true := by
  decide +kernel

theorem tot11618 : totK PD2M8K2 D2M8K2.t11618 = [0, 27811321821, 223181149897, 474334416769, 155486811965, 5159868635, 0, 0] := by
  decide +kernel

theorem rows11619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11619 = true := by
  decide +kernel

theorem tot11619 : totK PD2M8K2 D2M8K2.t11619 = [0, 167262455682, 444514310830, 274669302992, 30423867423, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
