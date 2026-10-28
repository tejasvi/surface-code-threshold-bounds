import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t616 = true := by
  decide +kernel

theorem tot616 : totK PD2M8K2 D2M8K2.t616 = [0, 177308436242, 470812863313, 222059885844, 13132442356, 0, 0, 0] := by
  decide +kernel

theorem rows617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t617 = true := by
  decide +kernel

theorem tot617 : totK PD2M8K2 D2M8K2.t617 = [0, 205614688503, 474343712011, 212252010617, 10101658128, 0, 0, 0] := by
  decide +kernel

theorem rows618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t618 = true := by
  decide +kernel

theorem tot618 : totK PD2M8K2 D2M8K2.t618 = [0, 208645484227, 479887822497, 204891651525, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t619 = true := by
  decide +kernel

theorem tot619 : totK PD2M8K2 D2M8K2.t619 = [152031495639, 331050457791, 287975133682, 140771616826, 13468148062, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
