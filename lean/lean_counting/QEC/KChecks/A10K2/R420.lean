import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1680 = true := by
  decide +kernel

theorem tot1680 : totK PA10K2 A10K2.t1680 = [0, 0, 140181680627, 1031999931273, 2010472373232, 1330279550871, 277000534609, 20070762815, 0, 0] := by
  decide +kernel

theorem rows1681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1681 = true := by
  decide +kernel

theorem tot1681 : totK PA10K2 A10K2.t1681 = [0, 0, 212862030042, 916336165329, 1885030122497, 1441221964262, 280382155887, 10747604052, 0, 0] := by
  decide +kernel

theorem rows1682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1682 = true := by
  decide +kernel

theorem tot1682 : totK PA10K2 A10K2.t1682 = [0, 0, 443847228748, 1698626855089, 1887047678440, 630973342751, 51464731716, 0, 0, 0] := by
  decide +kernel

theorem rows1683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1683 = true := by
  decide +kernel

theorem tot1683 : totK PA10K2 A10K2.t1683 = [0, 0, 122470450379, 1268343743508, 2322783582697, 960700384407, 66528807994, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
