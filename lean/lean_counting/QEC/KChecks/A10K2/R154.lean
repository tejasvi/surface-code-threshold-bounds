import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t616 = true := by
  decide +kernel

theorem tot616 : totK PA10K2 A10K2.t616 = [0, 0, 524712829483, 1900915340906, 1993778931539, 502534122368, 18535904725, 0, 0, 0] := by
  decide +kernel

theorem rows617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t617 = true := by
  decide +kernel

theorem tot617 : totK PA10K2 A10K2.t617 = [0, 0, 472925195016, 1799638057720, 1875188031539, 450241080646, 25681272668, 0, 0, 0] := by
  decide +kernel

theorem rows618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t618 = true := by
  decide +kernel

theorem tot618 : totK PA10K2 A10K2.t618 = [0, 0, 504013034742, 1756282994259, 1761903277360, 517766599094, 50718163417, 0, 0, 0] := by
  decide +kernel

theorem rows619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t619 = true := by
  decide +kernel

theorem tot619 : totK PA10K2 A10K2.t619 = [0, 0, 302031194261, 1529521229643, 2103064917561, 669048656725, 38148714322, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
