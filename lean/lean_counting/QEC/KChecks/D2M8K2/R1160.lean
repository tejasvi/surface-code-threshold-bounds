import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4640 = true := by
  decide +kernel

theorem tot4640 : totK PD2M8K2 D2M8K2.t4640 = [0, 0, 170241457764, 384724687284, 238678426759, 102094864700, 6784518318, 0] := by
  decide +kernel

theorem rows4641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4641 = true := by
  decide +kernel

theorem tot4641 : totK PD2M8K2 D2M8K2.t4641 = [0, 0, 162420916616, 452396453451, 261126710203, 18770509633, 0, 0] := by
  decide +kernel

theorem rows4642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4642 = true := by
  decide +kernel

theorem tot4642 : totK PD2M8K2 D2M8K2.t4642 = [0, 0, 89734097483, 339022998310, 383670840664, 81497481268, 1164319620, 0] := by
  decide +kernel

theorem rows4643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4643 = true := by
  decide +kernel

theorem tot4643 : totK PD2M8K2 D2M8K2.t4643 = [0, 0, 0, 265093189754, 487174998663, 140458119473, 7028279834, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
