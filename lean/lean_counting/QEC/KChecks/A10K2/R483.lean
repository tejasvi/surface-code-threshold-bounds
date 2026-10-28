import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1932 = true := by
  decide +kernel

theorem tot1932 : totK PA10K2 A10K2.t1932 = [0, 0, 0, 450914623231, 1610087617670, 1979295708101, 772324774876, 60578866985, 0, 0] := by
  decide +kernel

theorem rows1933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1933 = true := by
  decide +kernel

theorem tot1933 : totK PA10K2 A10K2.t1933 = [0, 0, 0, 384313791793, 1739915454993, 2064718253205, 627895279391, 44790206969, 0, 0] := by
  decide +kernel

theorem rows1934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1934 = true := by
  decide +kernel

theorem tot1934 : totK PA10K2 A10K2.t1934 = [0, 0, 0, 112528719203, 865524660498, 2082930647719, 1446695051924, 255682586580, 8047840951, 0] := by
  decide +kernel

theorem rows1935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1935 = true := by
  decide +kernel

theorem tot1935 : totK PA10K2 A10K2.t1935 = [0, 0, 0, 746768339096, 2209260957897, 1659345098280, 267610715761, 6241432281, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
