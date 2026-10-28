import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5784 = true := by
  decide +kernel

theorem tot5784 : totK PA10K2 A10K2.t5784 = [0, 0, 0, 128170967964, 927408342944, 2032525475575, 1245381456920, 192634754273, 5546304973, 0] := by
  decide +kernel

theorem rows5785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5785 = true := by
  decide +kernel

theorem tot5785 : totK PA10K2 A10K2.t5785 = [0, 0, 253038457361, 1113123890541, 1970982714849, 1428125468119, 253468608510, 9556858200, 0, 0] := by
  decide +kernel

theorem rows5786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5786 = true := by
  decide +kernel

theorem tot5786 : totK PA10K2 A10K2.t5786 = [0, 0, 425318706746, 1776651167899, 2025245657927, 573243650226, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5787 = true := by
  decide +kernel

theorem tot5787 : totK PA10K2 A10K2.t5787 = [0, 0, 88066441016, 835876812012, 1998091069183, 1526593377347, 342197832903, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
